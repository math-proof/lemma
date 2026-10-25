/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalAdmissibleSeamRow
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :=
  {row : SixVertexSector T.width sector.val //
    Nonempty ((i : Fin T.width) ->
      SixVertexVerticalColumnCompletionAtSeam T horizontal i
        (sixVertexSectorRow row i))}


end
end StatMech.FrontierD
