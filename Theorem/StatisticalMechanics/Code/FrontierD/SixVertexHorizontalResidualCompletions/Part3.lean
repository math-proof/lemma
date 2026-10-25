/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part2


namespace StatMech.FrontierD

noncomputable section

theorem configurationBigradeFibers_of_residualConfigurationHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      {pair : SixVertexMarkedSectorConfiguration T sourceLeft ×
          SixVertexMarkedSectorConfiguration T sourceRight //
        sixVertexConfigurationPairBigrade pair = grade} ->
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade} -> Prop)
    (hHall : SixVertexHorizontalActualDeficitTokenHall T
      sourceLeft sourceRight targetLeft targetRight
      (sixVertexHorizontalResidualConfigurationSupport T
        sourceLeft sourceRight targetLeft targetRight support)) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight :=
  configurationBigradeFibers_of_actualDeficitTokenHall T
    sourceLeft sourceRight targetLeft targetRight _ hHall

end
end StatMech.FrontierD
