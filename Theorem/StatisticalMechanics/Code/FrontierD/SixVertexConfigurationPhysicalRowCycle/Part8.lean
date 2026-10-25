/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPhysicalRowCycleOffDiagonal_branches_distinct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle) :
    sixVertexPhysicalRowCycleOffDiagonalForget target ≠
      sixVertexPhysicalRowCycleOffDiagonalSwap target := by
  intro heq
  exact target.2 (congrArg Prod.fst heq)

end
end StatMech.FrontierD
