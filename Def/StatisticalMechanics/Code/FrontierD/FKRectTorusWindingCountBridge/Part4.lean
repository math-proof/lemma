/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusAllChargeReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectCriticalWindingTailMass (R : FKRectTorus) (q : Real)
    (r : Nat) : Real :=
  ∑ omega : R.Configuration,
    if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
      fkRectCriticalRandomClusterProb R q omega
    else 0

end
end StatMech.FrontierD
