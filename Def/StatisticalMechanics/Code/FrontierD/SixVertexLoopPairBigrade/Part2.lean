/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopDecoratedPairBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) : Nat × Nat :=
  (sixVertexLoopDecoratedPairTotalC decorated,
    fkColoredTrueStrandSlotCount
      (sixVertexLoopDecoratedPairColored decorated))

end
end StatMech.FrontierD
