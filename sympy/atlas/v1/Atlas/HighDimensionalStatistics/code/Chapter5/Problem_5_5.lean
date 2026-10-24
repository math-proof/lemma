/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Problem_5_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Chapter5.Problem55

noncomputable section

/-- Sobolev ellipsoid of smoothness `β` and radius `Q`:
`{θ : ∑_j (j + 1)^{2β} θ_j² ≤ Q}` in `ℝ^d`. -/
def sobolevEllipsoid (d : ℕ) (β Q : ℝ) : Set (Fin d → ℝ) :=
  {θ | ∑ j : Fin d, ((j : ℝ) + 1) ^ (2 * β) * (θ j) ^ 2 ≤ Q}

/-- Minimax risk over the Sobolev ellipsoid (placeholder definition for
Problem 5.5). -/
end

end Chapter5.Problem55
