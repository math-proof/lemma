/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalFineProfilePair
    (T : EvenTorus) (profile : SixVertexHorizontalBoundedFineRowProfile T) :=
  {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T //
    sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile}


abbrev SixVertexHorizontalFineProfileCompletionPair
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :=
  Sigma fun horizontal : SixVertexHorizontalFineProfilePair T profile =>
    SixVertexHorizontalSectorCompletion T left horizontal.1.1 ×
      SixVertexHorizontalSectorCompletion T right horizontal.1.2


end
end StatMech.FrontierD
