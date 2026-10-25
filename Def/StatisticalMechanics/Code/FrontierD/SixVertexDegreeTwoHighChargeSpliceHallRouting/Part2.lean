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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting


namespace StatMech.FrontierD

noncomputable section

open Finset

noncomputable def sixVertexHorizontalDegreeTwoLoopSpliceTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  ⟨sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos hmiddle_lt
      source.1 key,
    (sixVertexLoopDecoratedSpliceUnitTarget_bigrade middle hmiddle_pos
      hmiddle_lt source.1 key).trans source.2⟩

end
end StatMech.FrontierD
