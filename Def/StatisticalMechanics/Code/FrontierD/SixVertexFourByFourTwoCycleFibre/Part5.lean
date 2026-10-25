/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part4


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAllowedHorizontalIndex (mask : Nat) : Fin 6 :=
  if mask = 0 then 0 else if mask = 3 then 1 else if mask = 6 then 2
  else if mask = 9 then 3 else if mask = 12 then 4 else 5

end
end StatMech.FrontierD
