/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourRowIndexEquiv : Fin 16 ≃ SixVertexRow 4 :=
  Equiv.ofBijective sixVertexFourRowOfIndex
    sixVertexFourRowOfIndex_bijective

end
end StatMech.FrontierD
