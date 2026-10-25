/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexVerticalCompletionToColumns
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    (i : Fin T.width) ->
      SixVertexVerticalColumnCompletion T horizontal i :=
  fun i =>
    ⟨fun j => completion.1 (i, j), fun j => by
      simpa [SixVertexArrows.incomingCount, sixVertexArrowsOfFields]
        using completion.2 (i, j)⟩


def sixVertexVerticalCompletionOfColumns
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (columns : (i : Fin T.width) ->
      SixVertexVerticalColumnCompletion T horizontal i) :
    SixVertexVerticalCompletion T horizontal :=
  ⟨fun v => (columns v.1).1 v.2, fun v => by
    simpa [SixVertexArrows.incomingCount, sixVertexArrowsOfFields]
      using (columns v.1).2 v.2⟩


def sixVertexVerticalCompletionEquivColumns
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T) :
    SixVertexVerticalCompletion T horizontal ≃
      ((i : Fin T.width) ->
        SixVertexVerticalColumnCompletion T horizontal i) where
  toFun := sixVertexVerticalCompletionToColumns
  invFun := sixVertexVerticalCompletionOfColumns
  left_inv completion := by
    apply Subtype.ext
    funext v
    rfl
  right_inv columns := by
    funext i
    apply Subtype.ext
    funext j
    rfl


end
end StatMech.FrontierD
