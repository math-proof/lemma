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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexLoopDecoratedPairFineProfileFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    Fintype.card
        (SixVertexLoopDecoratedPairFineProfileFiber T left right profile) =
      sixVertexHorizontalFineRowProfileSectorPairSum T left right profile *
        2 ^ (sixVertexHorizontalFineRowProfileGrade profile).1 := by
  rw [Fintype.card_congr
    (sixVertexLoopFineProfileFiberEquiv T left right profile)]
  rw [Fintype.card_prod,
    card_sixVertexConfigurationPairFineProfileFiber]
  simp


end
end StatMech.FrontierD
