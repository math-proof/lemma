module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusAllChargeReduction
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part3


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

def fkRectCriticalWindingTailMass (R : FKRectTorus) (q : Real)
    (r : Nat) : Real :=
  ∑ omega : R.Configuration,
    if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
      fkRectCriticalRandomClusterProb R q omega
    else 0

end
end StatMech.FrontierD
