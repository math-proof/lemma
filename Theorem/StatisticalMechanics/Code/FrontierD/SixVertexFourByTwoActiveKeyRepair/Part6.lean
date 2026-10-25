/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part6


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding_supported
    (source : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionKey) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade source.1
      (sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding source).1 := by
  rw [sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq source]
  exact sixVertexFourByTwoActiveObstructionToken_cycleRepair_supported

theorem sixVertexFourByTwoActiveObstructionCapacity_le_cycleRepair :
    sixVertexHorizontalActualDeficitFineUnionCapacity
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoActiveObstructionKey ≤
      sixVertexHorizontalActualSurplusFineUnionCapacity
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoActiveCycleRepairKey := by
  simpa only [sixVertexHorizontalActualDeficitFineUnionCapacity,
    sixVertexHorizontalActualSurplusFineUnionCapacity] using
      Fintype.card_le_of_embedding
        sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding


theorem sixVertexFourByTwoActiveObstruction_singletonKeyCapacityHall :
    (∑ key ∈ ({sixVertexFourByTwoActiveObstructionKey} :
        Finset (SixVertexPairFineUnionKey sixVertexFourByTwoTorus)),
      sixVertexHorizontalActualDeficitFineUnionCapacity
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade key) ≤
      ∑ key ∈ (Finset.univ.filter fun targetKey =>
          exists sourceKey,
            sourceKey ∈ ({sixVertexFourByTwoActiveObstructionKey} :
              Finset (SixVertexPairFineUnionKey sixVertexFourByTwoTorus)) ∧
            SixVertexPairFineUnionKeyTwoCycleRelated sourceKey targetKey),
        sixVertexHorizontalActualSurplusFineUnionCapacity
          sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
          sixVertexFourByTwoActiveObstructionMiddle_pos
          sixVertexFourByTwoActiveObstructionMiddle_lt
          sixVertexFourByTwoActiveObstructionGrade key := by
  simp only [Finset.sum_singleton]
  refine sixVertexFourByTwoActiveObstructionCapacity_le_cycleRepair.trans ?_
  apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨sixVertexFourByTwoActiveObstructionKey,
    Finset.mem_singleton_self _,
    sixVertexFourByTwoActiveObstructionKey_cycleRepair_related⟩

end
end StatMech.FrontierD
