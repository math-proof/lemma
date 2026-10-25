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


namespace StatMech.FrontierD

noncomputable section

def fkRectUnorientedVerticalWindingTotal
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  fkMedialUnorientedVerticalWindingTotal
    (fkRectConfigurationToMedialPairing R omega)


def fkRectUnorientedVerticalWindingNumber
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  fkRectUnorientedVerticalWindingTotal R omega / 2


end
end StatMech.FrontierD
