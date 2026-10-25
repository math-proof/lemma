/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalPairChooseWeight_eq_profile
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1 *
        sixVertexHorizontalSectorCompletionChooseCount T right horizontal.2 =
      sixVertexHorizontalPairProfileChooseWeight left right
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  rw [sixVertexHorizontalSectorCompletionChooseCount_eq_profile,
    sixVertexHorizontalSectorCompletionChooseCount_eq_profile]
  rfl


end
end StatMech.FrontierD
