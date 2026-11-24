module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusAllChargeReduction
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
