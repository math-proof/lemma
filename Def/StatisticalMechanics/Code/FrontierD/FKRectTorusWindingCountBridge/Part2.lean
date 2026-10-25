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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge


namespace StatMech.FrontierD

noncomputable section

def fkRectAllOrientedLoopTilt (R : FKRectTorus) (q lam : Real)
    (omega : R.Configuration) : Real :=
  (∑ arrows : SixVertexArrows R.medialTorus,
      fkRectOrientedLoopWeight R lam omega arrows) /
    fkRectCriticalReducedWeight R q omega


def fkRectZeroTurnLoopCount (R : FKRectTorus)
    (omega : R.Configuration) : Nat :=
  (Finset.univ.filter fun C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega) =>
    FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0).card


def fkRectNonzeroTurnLoopCount (R : FKRectTorus)
    (omega : R.Configuration) : Nat :=
  (Finset.univ.filter fun C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega) =>
    FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C ≠ 0).card

end
end StatMech.FrontierD
