/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part16


namespace StatMech.FrontierD

noncomputable section

open Finset

theorem loopBigradeFibers_of_degreeTwoLoopSpliceReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hreconnections : SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexLoopDecoratedPairBigradeFiberDominates T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle := by
  intro grade
  obtain ⟨reconnection⟩ := hreconnections grade
  exact Fintype.card_le_of_embedding reconnection.reconnectEmbedding

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hreconnections : SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers
    T middle hmiddle_pos hmiddle_lt
      (loopBigradeFibers_of_degreeTwoLoopSpliceReconnections
        T middle hmiddle_pos hmiddle_lt hreconnections)

end
end StatMech.FrontierD
