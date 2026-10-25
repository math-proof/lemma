/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalFineRowProfileAggregateSignedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade (rowProfile : SixVertexHorizontalRowZeroProfile T)
      (fineProfile : SixVertexHorizontalBoundedFineRowProfile T),
    0 <= ∑ horizontal ∈
        (Finset.univ : Finset
          (SixVertexHorizontalPairRowBigradeFiber T grade rowProfile)).filter
          (fun horizontal =>
            sixVertexHorizontalPairBoundedFineRowProfile horizontal.1 =
              fineProfile),
      sixVertexHorizontalProfileSignedKernel
        sourceLeft sourceRight targetLeft targetRight
        (sixVertexHorizontalPairCompletionProfile T horizontal.1)


end
end StatMech.FrontierD
