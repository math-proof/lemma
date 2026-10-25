/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part8
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectGraphCriticalReducedZ_eq
    (R : FKRectTorus) (q : Real) :
    fkRectGraphCriticalReducedZ R q = fkRectCriticalReducedZ R q := by
  unfold fkRectGraphCriticalReducedZ fkRectCriticalReducedZ
  symm
  apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
  intro omega
  exact fkRectGraphCriticalReducedWeight_configurationGraphEquiv R q omega |>.symm


end
end StatMech.FrontierD
