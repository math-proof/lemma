/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoActiveObstructionKey_eq_sourceKey :
    sixVertexFourByTwoActiveObstructionKey =
      sixVertexPairFineUnionKey
        (sixVertexFourByTwoLowArrows,
          sixVertexFourByTwoHighArrows) := by
  unfold sixVertexFourByTwoActiveObstructionKey
    sixVertexHorizontalActualDeficitFineUnionKey
  exact congrArg
    (fun pair => sixVertexPairFineUnionKey (pair.1.1, pair.2.1))
    sixVertexFourByTwoActiveObstructionConfigurationPair_eq


theorem sixVertexFourByTwoActiveObstructionKey_cycleRepair_related :
    SixVertexPairFineUnionKeyTwoCycleRelated
      sixVertexFourByTwoActiveObstructionKey sixVertexFourByTwoActiveCycleRepairKey := by
  rw [sixVertexFourByTwoActiveObstructionKey_eq_sourceKey]
  exact sixVertexPairFineUnionKeyTwoCycleRelated_complete
    sixVertexFourByTwo_cycleMiddle_fineRelated

theorem sixVertexFourByTwoActiveObstructionKey_ne_cycleRepairKey :
    sixVertexFourByTwoActiveObstructionKey ≠ sixVertexFourByTwoActiveCycleRepairKey := by
  rw [sixVertexFourByTwoActiveObstructionKey_eq_sourceKey]
  intro hkey
  have hhorizontal := congrArg SixVertexPairFineUnionKey.horizontal hkey
  have hvertical := congrArg SixVertexPairFineUnionKey.vertical hkey
  apply sixVertexFourByTwo_no_unionEqual_middlePair
    sixVertexFourByTwoCycleMiddleFirst
    sixVertexFourByTwoCycleMiddleSecond
    sixVertexFourByTwoCycleMiddleFirst_ice
    sixVertexFourByTwoCycleMiddleSecond_ice
    sixVertexFourByTwoCycleMiddleFirst_seamCount
  · funext v
    have h := congrFun hhorizontal v
    have hnat :
        (sixVertexFourByTwoLowArrows.horizontal v).toNat +
            (sixVertexFourByTwoHighArrows.horizontal v).toNat =
          (sixVertexFourByTwoCycleMiddleFirst.horizontal v).toNat +
            (sixVertexFourByTwoCycleMiddleSecond.horizontal v).toNat := by
      simpa [sixVertexFourByTwoActiveCycleRepairKey, sixVertexPairFineUnionKey] using h
    unfold sixVertexPairUnionHorizontal
    exact_mod_cast hnat
  · funext v
    have h := congrFun hvertical v
    have hnat :
        (sixVertexFourByTwoLowArrows.vertical v).toNat +
            (sixVertexFourByTwoHighArrows.vertical v).toNat =
          (sixVertexFourByTwoCycleMiddleFirst.vertical v).toNat +
            (sixVertexFourByTwoCycleMiddleSecond.vertical v).toNat := by
      simpa [sixVertexFourByTwoActiveCycleRepairKey, sixVertexPairFineUnionKey] using h
    unfold sixVertexPairUnionVertical
    exact_mod_cast hnat

theorem sixVertexFourByTwoActiveObstructionMiddle_pos :
    0 < sixVertexFourByTwoSectorOne.val := by
  norm_num [sixVertexFourByTwoSectorOne]

theorem sixVertexFourByTwoActiveObstructionMiddle_lt :
    sixVertexFourByTwoSectorOne.val < sixVertexFourByTwoTorus.width := by
  norm_num [sixVertexFourByTwoSectorOne, sixVertexFourByTwoTorus]

theorem sixVertexFourByTwoActiveObstructionDeficitCapacity_pos :
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey := by
  change 0 < Fintype.card
    {source : SixVertexHorizontalActualDeficitTokens
        sixVertexFourByTwoTorus sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
        sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne //
      sixVertexHorizontalActualDeficitFineUnionKey source =
        sixVertexFourByTwoActiveObstructionKey}
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨sixVertexFourByTwoActiveObstructionToken, rfl⟩⟩

theorem sixVertexFourByTwoActiveObstructionSurplusKeyFiber_isEmpty :
    IsEmpty
      (SixVertexHorizontalActualSurplusFineUnionKeyFiber
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey) := by
  constructor
  rintro ⟨target, hkey⟩
  have hkey' :
      sixVertexPairFineUnionKey
          ((sixVertexHorizontalActualSurplusConfigurationPair target).1.1.1,
            (sixVertexHorizontalActualSurplusConfigurationPair target).1.2.1) =
        sixVertexPairFineUnionKey
          (sixVertexFourByTwoLowArrows,
            sixVertexFourByTwoHighArrows) := by
    change sixVertexPairFineUnionKey
        ((sixVertexHorizontalActualSurplusConfigurationPair target).1.1.1,
          (sixVertexHorizontalActualSurplusConfigurationPair target).1.2.1) =
      sixVertexPairFineUnionKey
        ((sixVertexHorizontalActualDeficitConfigurationPair
          sixVertexFourByTwoActiveObstructionToken).1.1.1,
          (sixVertexHorizontalActualDeficitConfigurationPair
            sixVertexFourByTwoActiveObstructionToken).1.2.1) at hkey
    rw [sixVertexFourByTwoActiveObstructionConfigurationPair_eq] at hkey
    exact hkey
  have hhorizontal := congrArg SixVertexPairFineUnionKey.horizontal hkey'
  have hvertical := congrArg SixVertexPairFineUnionKey.vertical hkey'
  apply sixVertexFourByTwo_no_unionEqual_middlePair
    (sixVertexHorizontalActualSurplusConfigurationPair target).1.1.1
    (sixVertexHorizontalActualSurplusConfigurationPair target).1.2.1
  · exact (sixVertexHorizontalActualSurplusConfigurationPair target).1.1.2.1
  · exact (sixVertexHorizontalActualSurplusConfigurationPair target).1.2.2.1
  · exact (sixVertexHorizontalActualSurplusConfigurationPair target).1.1.2.2
  · funext v
    have h := congrFun hhorizontal v
    have hnat :
        (sixVertexFourByTwoLowArrows.horizontal v).toNat +
            (sixVertexFourByTwoHighArrows.horizontal v).toNat =
          (((sixVertexHorizontalActualSurplusConfigurationPair
            target).1.1.1.horizontal v).toNat +
            ((sixVertexHorizontalActualSurplusConfigurationPair
              target).1.2.1.horizontal v).toNat) := by
      simpa [sixVertexPairFineUnionKey] using h.symm
    unfold sixVertexPairUnionHorizontal
    exact_mod_cast hnat
  · funext v
    have h := congrFun hvertical v
    have hnat :
        (sixVertexFourByTwoLowArrows.vertical v).toNat +
            (sixVertexFourByTwoHighArrows.vertical v).toNat =
          (((sixVertexHorizontalActualSurplusConfigurationPair
            target).1.1.1.vertical v).toNat +
            ((sixVertexHorizontalActualSurplusConfigurationPair
              target).1.2.1.vertical v).toNat) := by
      simpa [sixVertexPairFineUnionKey] using h.symm
    unfold sixVertexPairUnionVertical
    exact_mod_cast hnat


theorem sixVertexFourByTwo_not_reflexiveActiveFiberEmbeddings :
    ¬ SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt := by
  intro hembeddings
  obtain ⟨embedding⟩ := hembeddings sixVertexFourByTwoActiveObstructionGrade
    sixVertexFourByTwoActiveObstructionKey sixVertexFourByTwoActiveObstructionDeficitCapacity_pos
  let source : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey :=
    ⟨sixVertexFourByTwoActiveObstructionToken, rfl⟩
  exact sixVertexFourByTwoActiveObstructionSurplusKeyFiber_isEmpty.false (embedding source)

end
end StatMech.FrontierD
