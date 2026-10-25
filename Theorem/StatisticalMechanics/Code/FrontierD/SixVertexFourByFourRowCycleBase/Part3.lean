/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part3


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem sixVertexFourHorizontalTransitionCount_certificate :
    ∀ previous current : Fin 16,
      sixVertexHorizontalTransitionCountExecutable
          (T := sixVertexFourByFourTorus)
          (sixVertexFourRowOfIndex previous)
          (sixVertexFourRowOfIndex current) =
        sixVertexFourHorizontalTransitionCount previous current := by
  decide +revert

end
end StatMech.FrontierD
