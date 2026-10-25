/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPairBigradeFiberDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade,
    Fintype.card
        {source : SixVertexMarkedSectorConfiguration T sourceLeft ×
            SixVertexMarkedSectorConfiguration T sourceRight //
          sixVertexConfigurationPairBigrade source = grade} <=
      Fintype.card
        {target : SixVertexMarkedSectorConfiguration T targetLeft ×
            SixVertexMarkedSectorConfiguration T targetRight //
          sixVertexConfigurationPairBigrade target = grade}

end
end StatMech.FrontierD
