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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part19


namespace StatMech.FrontierD

noncomputable section

open Finset

theorem degreeTwoLoopSpliceReconnections_of_selectedOutputResolvedCrossDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoders
        T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨decoded⟩ := hdecoded grade
  exact ⟨decoded.toSpliceReconnection⟩

theorem
    sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputResolvedCrossDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoders
        T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections
    T middle hmiddle_pos hmiddle_lt
      (degreeTwoLoopSpliceReconnections_of_selectedOutputResolvedCrossDecoders
        T middle hmiddle_pos hmiddle_lt hdecoded)

theorem degreeTwoLoopSpliceReconnections_of_selectedOutputFullMaskDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoders
        T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨decoded⟩ := hdecoded grade
  exact ⟨decoded.toSpliceReconnection⟩

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputFullMaskDecoders
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded :
      SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoders
        T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections
    T middle hmiddle_pos hmiddle_lt
      (degreeTwoLoopSpliceReconnections_of_selectedOutputFullMaskDecoders
        T middle hmiddle_pos hmiddle_lt hdecoded)

end
end StatMech.FrontierD
