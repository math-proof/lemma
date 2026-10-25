/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part9


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedRepairColumns
    (firstSeam secondSeam : Fin 4) : Fin 4 × Fin 4 :=
  (![1, 0, 1, 0] firstSeam,
    if firstSeam.val % 2 = 0 then ![2, 1, 2, 1] secondSeam
    else ![0, 3, 0, 3] secondSeam)

end
end StatMech.FrontierD
