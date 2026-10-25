/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexVerticalCompletionSeamRow
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    SixVertexRow T.width :=
  fun i => completion.1 (i, svFinLast T.height_pos)

end
end StatMech.FrontierD
