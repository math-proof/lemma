module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part9
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectGraphCriticalRandomClusterProb (R : FKRectTorus) (q : Real)
    (eta : FKRectGraphConfiguration R) : Real :=
  fkRectGraphCriticalReducedWeight R q eta /
    fkRectGraphCriticalReducedZ R q


end
end StatMech.FrontierD
