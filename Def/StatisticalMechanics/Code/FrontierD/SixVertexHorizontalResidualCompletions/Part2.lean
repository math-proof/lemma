/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalResidualConfigurationSupport
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      {pair : SixVertexMarkedSectorConfiguration T sourceLeft ×
          SixVertexMarkedSectorConfiguration T sourceRight //
        sixVertexConfigurationPairBigrade pair = grade} ->
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade} -> Prop) :
    forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop :=
  fun grade source target =>
    support grade
      (sixVertexHorizontalActualDeficitConfigurationPair source)
      (sixVertexHorizontalActualSurplusConfigurationPair target)

end
end StatMech.FrontierD
