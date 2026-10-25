/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexConfigurationPairTwoCycleFineRelated.totalC
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {source : SixVertexMarkedPairSource T lower upper}
    {target : SixVertexMarkedPairTarget T middle}
    (hrelated : SixVertexConfigurationPairTwoCycleFineRelated source target) :
    sixVertexConfigurationPairTotalC source =
      sixVertexConfigurationPairTotalC target := by
  exact sixVertexPairAtMostTwoCycleFineRelated_totalC hrelated


end
end StatMech.FrontierD
