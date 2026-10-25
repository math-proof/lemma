/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexArrowsOfFields
    {T : EvenTorus} (horizontal vertical : T.Vertex -> Bool) :
    SixVertexArrows T where
  horizontal := horizontal
  vertical := vertical


end
end StatMech.FrontierD
