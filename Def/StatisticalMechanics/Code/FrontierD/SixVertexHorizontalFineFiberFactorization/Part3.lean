/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalSingleRowProfileSectorSum
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedSingleRowProfile T) : Nat :=
  ∑ horizontal : SixVertexHorizontalField T,
    if sixVertexHorizontalBoundedSingleRowProfile horizontal = profile then
      sixVertexHorizontalSectorCompletionChooseCount T sector horizontal
    else 0


def sixVertexHorizontalFineRowProfileSectorPairSum
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) : Nat :=
  ∑ horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T,
    if sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile then
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1 *
        sixVertexHorizontalSectorCompletionChooseCount T right horizontal.2
    else 0

end
end StatMech.FrontierD
