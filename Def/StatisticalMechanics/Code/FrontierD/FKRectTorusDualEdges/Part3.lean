/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectDualConfigurationEquiv (R : FKRectTorus) :
    R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectEdgeDualEquiv R) Equiv.boolNot

end
end StatMech.FrontierD
