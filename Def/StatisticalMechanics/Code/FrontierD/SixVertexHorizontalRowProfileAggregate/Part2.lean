/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalRowProfileAggregateSignedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade (rowProfile : SixVertexHorizontalRowZeroProfile T),
    0 <= ∑ horizontal :
        SixVertexHorizontalPairRowBigradeFiber T grade rowProfile,
      sixVertexHorizontalProfileSignedKernel
        sourceLeft sourceRight targetLeft targetRight
        (sixVertexHorizontalPairCompletionProfile T horizontal.1)

end
end StatMech.FrontierD
