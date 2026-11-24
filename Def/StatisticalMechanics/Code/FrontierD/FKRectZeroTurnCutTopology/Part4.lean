module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutTopology.Part3
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectZeroTurnCutRemainderCount
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  (fkRectZeroTurnCutRemainderComponents R omega).card


end
end StatMech.FrontierD
