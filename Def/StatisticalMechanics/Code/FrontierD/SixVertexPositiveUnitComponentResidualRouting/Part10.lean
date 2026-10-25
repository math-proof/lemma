/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part7


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalResidualHighBaseKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (single : SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed
        (sixVertexHorizontalHallHighSourceCanonicalLoop source))) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored
        (sixVertexHorizontalHallSourceCanonicalLoop source.1).1) :=
  FKColoredFineTwoCycleUnitTransferSpliceKey.ofRoutedKey
    (sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration
      (sixVertexHorizontalHallSourceCanonicalLoop source.1).1
      (sixVertexHorizontalDegreeTwoLoopHighChargeDegree
        (sixVertexHorizontalHallHighSourceCanonicalLoop source))
      single.toFineRoutedKey)


noncomputable def sixVertexHorizontalResidualHighBranchKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (single : SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed
        (sixVertexHorizontalHallHighSourceCanonicalLoop source)))
    (branch : Bool) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored
        (sixVertexHorizontalHallSourceCanonicalLoop source.1).1) :=
  (sixVertexHorizontalResidualHighBaseKey source single).paired
    (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo
      (sixVertexHorizontalHallSourceCanonicalLoop source.1)) branch


end
end StatMech.FrontierD
