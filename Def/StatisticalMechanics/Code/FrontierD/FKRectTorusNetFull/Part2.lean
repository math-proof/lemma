/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectHorizontalFundamentalWalk (R : FKRectTorus) :
    (fkRectFullOpenGraph R).Walk (fkRectOrigin R) (fkRectOrigin R) :=
  (fkRectHorizontalFundamentalWalkAux R
    (⟨0, R.width_pos⟩ : Fin R.width) R.width).copy rfl (by
      unfold fkRectOrigin
      rw [fkRectCyclicPred_iterate_zero_card])

noncomputable def fkRectVerticalFundamentalWalk (R : FKRectTorus) :
    (fkRectFullOpenGraph R).Walk (fkRectOrigin R) (fkRectOrigin R) :=
  (fkRectVerticalFundamentalWalkAux R
    (⟨0, R.width_pos⟩ : Fin R.width)
    (⟨0, R.height_pos⟩ : Fin R.height) R.height).copy rfl (by
      unfold fkRectOrigin
      rw [fkRectCyclicPred_iterate_zero_card])

end
end StatMech.FrontierD
