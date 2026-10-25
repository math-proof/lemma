/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem configurationPairTwoCycleFineHall_iff_exists_injective
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) :
    SixVertexConfigurationPairTwoCycleFineHall T lower middle upper <->
      exists matching : SixVertexMarkedPairSource T lower upper ->
          SixVertexMarkedPairTarget T middle,
        Function.Injective matching /\
          forall source,
            SixVertexConfigurationPairTwoCycleFineRelated
              source (matching source) := by
  unfold SixVertexConfigurationPairTwoCycleFineHall
  exact Fintype.all_card_le_filter_rel_iff_exists_injective
    SixVertexConfigurationPairTwoCycleFineRelated


end
end StatMech.FrontierD
