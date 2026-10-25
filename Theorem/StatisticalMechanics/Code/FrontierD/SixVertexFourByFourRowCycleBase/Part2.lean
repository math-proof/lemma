/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFourRowIndexEquiv_apply (index : Fin 16) :
    sixVertexFourRowIndexEquiv index = sixVertexFourRowOfIndex index := rfl

end
end StatMech.FrontierD
