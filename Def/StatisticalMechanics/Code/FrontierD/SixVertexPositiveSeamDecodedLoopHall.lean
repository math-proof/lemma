/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexArrows T × SixVertexArrows T :=
  (source.1.1.1.1, source.1.1.2.1)


def sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
    {T : EvenTorus} {middle : Fin (T.width + 1)} {grade : Nat × Nat}
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    SixVertexArrows T × SixVertexArrows T :=
  (target.1.1.1.1, target.1.1.2.1)


def sixVertexHorizontalDegreeTwoLoopRoutedSignedTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1))
    (family : SixVertexAtMostTwoCycleFamily T) (sign : Bool)
    (horizontalDelta : sixVertexPairUnionHorizontalDelta
        (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source)
        (sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key)) =
      fun v => if sign then family.horizontalFlow v
        else -family.horizontalFlow v)
    (verticalDelta : sixVertexPairUnionVerticalDelta
        (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source)
        (sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key)) =
      fun v => if sign then family.verticalFlow v
        else -family.verticalFlow v) :
    SixVertexSignedWindingCycleTarget
      (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source)
      family sign where
  target := sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
    (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key)
  horizontalDelta := horizontalDelta
  verticalDelta := verticalDelta


end
end StatMech.FrontierD
