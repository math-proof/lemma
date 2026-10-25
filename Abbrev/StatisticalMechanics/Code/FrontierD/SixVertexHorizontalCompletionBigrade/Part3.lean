/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexVerticalColumnCompletion
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) :=
  {column : Fin T.height -> Bool // forall j,
    (horizontal
          (SixVertexArrows.cyclicPred T.width_pos i, j)).toNat +
        (!horizontal (i, j)).toNat +
        (column (SixVertexArrows.cyclicPred T.height_pos j)).toNat +
        (!column j).toNat = 2}


end
end StatMech.FrontierD
