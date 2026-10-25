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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexVerticalRowsInSector
    (T : EvenTorus) (sector : Fin (T.width + 1)) :=
  {vertical : Fin T.height → SixVertexRow T.width //
    sixVertexUpCount (vertical (svFinLast T.height_pos)) = sector.val}


abbrev SixVertexHorizontalTransitionWitness
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width)
    (j : Fin T.height) :=
  {horizontal : SixVertexRow T.width //
    svHorizontalIce T.width_pos
      (vertical (SixVertexArrows.cyclicPred T.height_pos j))
      (vertical j) horizontal}


end
end StatMech.FrontierD
