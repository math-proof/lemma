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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge.Part2


namespace StatMech.FrontierD

noncomputable section

def SixVertexLoopDecoratedPairFineProfileFiberDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall profile : SixVertexHorizontalBoundedFineRowProfile T,
    Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber
      T sourceLeft sourceRight profile) <=
    Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber
      T targetLeft targetRight profile)


end
end StatMech.FrontierD
