/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectConfigurationGraphEquiv (R : FKRectTorus) :
    R.Configuration ≃ FKRectGraphConfiguration R where
  toFun omega e := omega ((fkRectEdgeGraphEquiv R).symm e)
  invFun eta a := eta (fkRectEdgeGraphEquiv R a)
  left_inv omega := by
    funext a
    simp
  right_inv eta := by
    funext e
    simp

end
end StatMech.FrontierD
