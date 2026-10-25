/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall


namespace StatMech.FrontierD

noncomputable section

structure SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  key : ∀ source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade,
    Bool → FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade
  decode_target : ∀ source branch,
    decode (sixVertexHorizontalDegreeTwoLoopRoutedTarget source
      (key source branch)) = source
  firstSigned : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    SixVertexSignedWindingCycleTarget
      (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source.1)
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source).firstWindingFamily
      true
  first_target : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    (firstSigned source).target =
      sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
        (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
          (key source.1 false))
  secondSigned : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    SixVertexSignedWindingCycleTarget
      (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source.1)
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source).secondWindingFamily
      true
  second_target : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    (secondSigned source).target =
      sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
        (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
          (key source.1 true))

end
end StatMech.FrontierD
