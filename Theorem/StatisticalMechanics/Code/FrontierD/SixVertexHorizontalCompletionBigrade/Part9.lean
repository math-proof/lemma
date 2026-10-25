/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part11
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem configurationBigradeFibers_iff_horizontalChooseBigradeFibers
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexConfigurationPairBigradeFiberDominates T
        sourceLeft sourceRight targetLeft targetRight <->
      SixVertexHorizontalChooseBigradeFiberDominates T
        sourceLeft sourceRight targetLeft targetRight := by
  constructor <;> intro hfiber grade
  · rw [<- card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums,
      <- card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums]
    exact hfiber grade
  · rw [card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums,
      card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums]
    exact hfiber grade

end
end StatMech.FrontierD
