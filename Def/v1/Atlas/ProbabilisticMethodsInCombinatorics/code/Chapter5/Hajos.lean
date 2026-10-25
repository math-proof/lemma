/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Choose.Bounds
open Filter Topology Real Asymptotics SimpleGraph

set_option maxHeartbeats 400000


namespace Hajos

/-- The threshold $t = \lceil 10 \sqrt{n} \rceil$ used in Theorem 5.3.2: we show that
$G(n, 1/2)$ has no $K_t$-subdivision with high probability. -/
noncomputable def hajosParam (n : ℕ) : ℕ := ⌈10 * Real.sqrt (n : ℝ)⌉₊

/-- The union bound on the probability that $G(n, 1/2)$ contains a $K_t$-subdivision,
for $t = \lceil 10\sqrt n \rceil$: $\binom{n}{t} \cdot e^{-t^2/10}$. -/
noncomputable def subdivisionUnionBound (n : ℕ) : ℝ :=
  (n.choose (hajosParam n) : ℝ) * Real.exp (-(hajosParam n : ℝ) ^ 2 / 10)

end Hajos
