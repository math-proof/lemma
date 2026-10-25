/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (source : SixVertexHorizontalFineProfileCompletionPair
      T lower upper profile)
    (target : SixVertexHorizontalFineProfileCompletionPair
      T middle middle profile) : Prop :=
  sixVertexPairAtMostTwoCycleRelated
    (sixVertexHorizontalFineProfileCompletionPairArrows source)
    (sixVertexHorizontalFineProfileCompletionPairArrows target)


def SixVertexHorizontalFineProfileCompletionPairUnionEqual
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (source : SixVertexHorizontalFineProfileCompletionPair
      T lower upper profile)
    (target : SixVertexHorizontalFineProfileCompletionPair
      T middle middle profile) : Prop :=
  let sourceArrows :=
    sixVertexHorizontalFineProfileCompletionPairArrows source
  let targetArrows :=
    sixVertexHorizontalFineProfileCompletionPairArrows target
  sixVertexPairUnionHorizontal sourceArrows =
      sixVertexPairUnionHorizontal targetArrows /\
    sixVertexPairUnionVertical sourceArrows =
      sixVertexPairUnionVertical targetArrows

end
end StatMech.FrontierD
