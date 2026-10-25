/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall.Part2


namespace StatMech.FrontierD

noncomputable section

theorem degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopRoutedReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨data⟩ := hdecoded grade
  exact ⟨data.toRoutedReconnection⟩


theorem loopBigradeFibers_of_decodedWindingReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexLoopDecoratedPairBigradeFiberDominates T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle :=
  loopBigradeFibers_of_degreeTwoLoopRoutedReconnections T middle
    hmiddle_pos hmiddle_lt
    (degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt hdecoded)


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedWindingReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopRoutedReconnections
    T middle hmiddle_pos hmiddle_lt
    (degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections
      T middle hmiddle_pos hmiddle_lt hdecoded)

end
end StatMech.FrontierD
