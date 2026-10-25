/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectConfigurationGraphEquiv_apply_edge
    (R : FKRectTorus) (omega : R.Configuration) (a : R.EdgeIndex) :
    fkRectConfigurationGraphEquiv R omega (fkRectEdgeGraphEquiv R a) =
      omega a := by
  simp [fkRectConfigurationGraphEquiv]


end
end StatMech.FrontierD
