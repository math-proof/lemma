/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoStepCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoStepCount.Part2


namespace StatMech.FrontierD

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sixVertexFourDynamicGradeCount_zero_test :
    sixVertexFourDynamicGradeCount sixVertexFourByFourSectorZero 0 = 16 := by
  decide +revert

end StatMech.FrontierD
