/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopDecoratedUnitTransfer
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexLoopDecoratedPairFineProfileFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :=
  {decorated : SixVertexLoopDecoratedPair T left right //
    sixVertexHorizontalPairBoundedFineRowProfile
      ((sixVertexLoopDecoratedPairColored decorated false).arrows.horizontal,
        (sixVertexLoopDecoratedPairColored decorated true).arrows.horizontal) =
      profile}

end
end StatMech.FrontierD
