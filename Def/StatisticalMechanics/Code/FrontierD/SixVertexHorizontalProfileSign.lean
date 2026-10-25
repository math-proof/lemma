/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileSign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalProfileSignedKernel
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) : Int :=
  (sixVertexHorizontalPairProfileChooseWeight
      targetLeft targetRight profile : Int) -
    sixVertexHorizontalPairProfileChooseWeight
      sourceLeft sourceRight profile


def SixVertexHorizontalProfileAggregateSignedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade,
    0 <= ∑ profile : SixVertexHorizontalPairCompletionProfile T,
      (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
        sixVertexHorizontalProfileSignedKernel
          sourceLeft sourceRight targetLeft targetRight profile


end
end StatMech.FrontierD
