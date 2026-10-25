/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexCheckerHorizontalZeroCount_eq_horizontal
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexCheckerHorizontalZeroCount omega =
      sixVertexHorizontalZeroCount omega.horizontal := by
  rfl

@[simp] theorem sixVertexCheckerHorizontalNontransitionCount_eq_horizontal
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexCheckerHorizontalNontransitionCount omega =
      sixVertexHorizontalNontransitionCount omega.horizontal := by
  rfl


theorem sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) :
    sixVertexConfigurationPairBigrade pair =
      sixVertexHorizontalPairBigrade
        (pair.1.1.horizontal, pair.2.1.horizontal) := by
  unfold sixVertexConfigurationPairBigrade
    sixVertexConfigurationPairTotalC sixVertexHorizontalPairBigrade
  rw [sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount,
    sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount,
    sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_zeroCount]
  rfl


end
end StatMech.FrontierD
