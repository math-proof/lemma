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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

structure SixVertexPhysicalRowCyclePairedBranchEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  branch : Bool →
    SixVertexPhysicalRowCycleSource T middle hmiddle_pos hmiddle_lt ↪
      SixVertexPhysicalRowCycleTarget T middle
  distinct : forall source, branch false source ≠ branch true source
  aggregateTotalC : forall source,
    2 * sixVertexPhysicalRowCyclePairTotalC source <=
      sixVertexPhysicalRowCyclePairTotalC (branch false source) +
        sixVertexPhysicalRowCyclePairTotalC (branch true source)

end
end StatMech.FrontierD
