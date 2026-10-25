/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWeightedQuadrature


namespace StatMech.FrontierD

noncomputable section

def sixVertexCyclicRootPartition {n : Nat}
    (p : Fin (n + 1) → Real) : Nat → Real
  | 0 => p (Fin.last n) - 2 * Real.pi
  | k + 1 => p ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩

end
end StatMech.FrontierD
