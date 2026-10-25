/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRepairDecodedLoopHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall.Part2


namespace StatMech.FrontierD

noncomputable section

structure SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair
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
  family : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade → SixVertexAtMostTwoCycleFamily T
  repair : ∀ source :
      SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    SixVertexSignedWindingCycleTarget
      (sixVertexHorizontalDegreeTwoLoopHallSourceArrowPair source.1)
      (family source) true
  repair_layers_ne : ∀ source,
    (repair source).target.1 ≠ (repair source).target.2
  first_target : ∀ source,
    (repair source).target =
      sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
        (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
          (key source.1 false))
  second_target : ∀ source,
    (repair source).swapTarget.target =
      sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
        (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
          (key source.1 true))

end
end StatMech.FrontierD
