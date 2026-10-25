/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy.Part6
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectCriticalZeroTurnAtMostMass
    (R : FKRectTorus) (q : Real) (L : Nat) : Real :=
  ∑ omega : R.Configuration,
    if fkRectZeroTurnLoopCount R omega ≤ L then
      fkRectCriticalRandomClusterProb R q omega
    else 0


def fkRectCriticalZeroTurnAboveMass
    (R : FKRectTorus) (q : Real) (L : Nat) : Real :=
  ∑ omega : R.Configuration,
    if L < fkRectZeroTurnLoopCount R omega then
      fkRectCriticalRandomClusterProb R q omega
    else 0


def fkRectCriticalZeroTurnExpectation
    (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : R.Configuration,
    fkRectCriticalRandomClusterProb R q omega *
      fkRectZeroTurnLoopCount R omega

end
end StatMech.FrontierD
