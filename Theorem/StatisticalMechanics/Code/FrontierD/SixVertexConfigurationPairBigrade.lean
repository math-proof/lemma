/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexLoopDecoratedPairBigradeFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    Fintype.card
        {decorated : SixVertexLoopDecoratedPair T left right //
          sixVertexLoopDecoratedPairBigrade decorated = grade} =
      Fintype.card
          {pair : SixVertexMarkedSectorConfiguration T left ×
              SixVertexMarkedSectorConfiguration T right //
            sixVertexConfigurationPairBigrade pair = grade} *
        2 ^ grade.1 := by
  rw [Fintype.card_congr
    (sixVertexLoopDecoratedPairBigradeFiberEquiv T left right grade)]
  simp

end
end StatMech.FrontierD
