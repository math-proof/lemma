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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectZeroTurnEulerResidual (R : FKRectTorus) (q : Real)
    (omega : R.Configuration) : Real :=
  (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
    Real.sqrt q ^ fkRectEulerHomologyDefect R omega

end
end StatMech.FrontierD
