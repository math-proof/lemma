/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Problem_5_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open scoped ENNReal


namespace Chapter5.Problem53

noncomputable section

/-- `S` is an `ε`-packing of the unit ball in `ℝ^d`: every point has norm at
most `1`, and any two distinct points are separated by at least `2ε`. -/
def IsEpsPacking {d : ℕ} (ε : ℝ) (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ x ∈ S, ‖x‖ ≤ 1) ∧
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≥ 2 * ε)

end
end Chapter5.Problem53
