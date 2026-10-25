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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexMarkedSectorRowCycle
    (T : EvenTorus) (sector : Fin (T.width + 1)) :=
  {rows : (Fin T.height → SixVertexRow T.width) ×
      (Fin T.height → SixVertexRow T.width) //
    (forall j,
      svHorizontalIce T.width_pos
        (rows.2 (SixVertexArrows.cyclicPred T.height_pos j))
        (rows.2 j) (rows.1 j)) ∧
      sixVertexUpCount (rows.2 (svFinLast T.height_pos)) = sector.val}

end
end StatMech.FrontierD
