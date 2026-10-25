/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalProfileAggregateDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade,
    (∑ profile : SixVertexHorizontalPairCompletionProfile T,
      sixVertexHorizontalPairProfileMultiplicity T grade profile *
        sixVertexHorizontalPairProfileChooseWeight
          sourceLeft sourceRight profile) <=
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        sixVertexHorizontalPairProfileMultiplicity T grade profile *
          sixVertexHorizontalPairProfileChooseWeight
            targetLeft targetRight profile


end
end StatMech.FrontierD
