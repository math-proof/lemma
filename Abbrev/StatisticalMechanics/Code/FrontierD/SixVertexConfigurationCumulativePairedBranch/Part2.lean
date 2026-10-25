/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationCumulativePairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationCumulativePairedBranch


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexConfigurationCumulativePairedBranchEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :=
  TwoBranchMonotoneEmbeddings
    (SixVertexConfigurationCumulativeSource T middle hmiddle_pos hmiddle_lt)
    (SixVertexConfigurationCumulativeTarget T middle)
    sixVertexConfigurationCumulativeTotalC
    sixVertexConfigurationCumulativeTotalC

end
end StatMech.FrontierD
