/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CorrelationReduction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareGluing.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisLimit.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorThermodynamicBridge
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectFixedChargeVerticalFamily (r k m : Nat) : FKRectTorus where
  width := 2 * (r + k + 2)
  height := 2 * (m + 2)
  width_gt_two := by omega
  height_gt_two := by omega
  height_even := ⟨m + 2, by omega⟩

end
end StatMech.FrontierD
