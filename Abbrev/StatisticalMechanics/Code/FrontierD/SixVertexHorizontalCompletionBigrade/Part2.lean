/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexVerticalCompletion
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T) :=
  {vertical : T.Vertex -> Bool //
    (sixVertexArrowsOfFields horizontal vertical).IceRule}


abbrev SixVertexHorizontalSectorCompletion
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :=
  {completion : SixVertexVerticalCompletion T horizontal //
    sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexArrowsOfFields horizontal completion.1)
      (svFinLast T.height_pos)) = sector.val}


end
end StatMech.FrontierD
