/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalSectorCompletionChooseCount
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) : Nat :=
  if Nonempty (SixVertexVerticalCompletion T horizontal) then
    if (sixVertexHorizontalForcedTrueColumns horizontal).card <= sector.val
    then Nat.choose
      ((sixVertexHorizontalTrueAllowedColumns horizontal).card -
        (sixVertexHorizontalForcedTrueColumns horizontal).card)
      (sector.val -
        (sixVertexHorizontalForcedTrueColumns horizontal).card)
    else 0
  else 0

end
end StatMech.FrontierD
