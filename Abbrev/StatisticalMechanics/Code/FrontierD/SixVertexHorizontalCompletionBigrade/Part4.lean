/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexVerticalColumnCompletionAtSeam
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) (seam : Bool) :=
  {column : SixVertexVerticalColumnCompletion T horizontal i //
    column.1 (svFinLast T.height_pos) = seam}

end
end StatMech.FrontierD
