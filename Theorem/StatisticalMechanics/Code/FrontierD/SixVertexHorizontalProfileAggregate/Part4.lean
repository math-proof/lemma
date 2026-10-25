/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem horizontalChooseBigradeFibers_iff_profileAggregate
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalChooseBigradeFiberDominates T
        sourceLeft sourceRight targetLeft targetRight ↔
      SixVertexHorizontalProfileAggregateDominates T
        sourceLeft sourceRight targetLeft targetRight := by
  constructor <;> intro hdom grade
  · rw [<- sixVertexHorizontalChooseSum_eq_profileAggregate,
      <- sixVertexHorizontalChooseSum_eq_profileAggregate]
    exact hdom grade
  · rw [sixVertexHorizontalChooseSum_eq_profileAggregate,
      sixVertexHorizontalChooseSum_eq_profileAggregate]
    exact hdom grade

end
end StatMech.FrontierD
