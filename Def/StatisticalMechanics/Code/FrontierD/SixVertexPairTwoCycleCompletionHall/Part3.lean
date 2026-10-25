/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part2


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalFineProfileCompletionTwoCycleMatching
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall profile : SixVertexHorizontalBoundedFineRowProfile T,
    exists matching :
        SixVertexHorizontalFineProfileCompletionPair
            T lower upper profile ->
          SixVertexHorizontalFineProfileCompletionPair
            T middle middle profile,
      Function.Injective matching /\
        forall source,
          SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
            source (matching source)


def SixVertexHorizontalFineProfileCompletionUnionMatching
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall profile : SixVertexHorizontalBoundedFineRowProfile T,
    exists matching :
        SixVertexHorizontalFineProfileCompletionPair
            T lower upper profile ->
          SixVertexHorizontalFineProfileCompletionPair
            T middle middle profile,
      Function.Injective matching /\
        forall source,
          SixVertexHorizontalFineProfileCompletionPairUnionEqual
            source (matching source)


end
end StatMech.FrontierD
