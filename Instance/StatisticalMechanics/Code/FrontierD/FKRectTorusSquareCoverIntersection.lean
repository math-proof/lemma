/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part6
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

instance fkRectSquareCoverSide_neZero (R : FKRectTorus) :
    NeZero (fkRectSquareCoverSide R) :=
  ⟨ne_of_gt (lt_trans (by norm_num : 0 < 2)
    (fkRectSquareCoverSide_gt_two R))⟩

instance fkRectSquareCoverSide_fact (R : FKRectTorus) :
    Fact (2 < fkRectSquareCoverSide R) :=
  ⟨fkRectSquareCoverSide_gt_two R⟩


end
end StatMech.FrontierD
