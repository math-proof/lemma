/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part7
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectGraphCriticalReducedWeight_configurationGraphEquiv
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectGraphCriticalReducedWeight R q
        (fkRectConfigurationGraphEquiv R omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectGraphCriticalReducedWeight fkRectCriticalReducedWeight
  rw [fkRectGraphOpenEdgeCount_configurationGraphEquiv,
    fkRectGraph_clusterCount_configurationGraphEquiv]


end
end StatMech.FrontierD
