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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part14


namespace StatMech.FrontierD

noncomputable section

open Finset

abbrev SixVertexHorizontalDegreeTwoLoopFullUnitMask
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :=
  {mask : SixVertexArrows T //
    SixVertexFullDisagreementMask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows mask ∧
      sixVertexTorusMaskSeamTransfer mask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1}

end
end StatMech.FrontierD
