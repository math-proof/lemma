module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectDualConfigurationEquiv (R : FKRectTorus) :
    R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectEdgeDualEquiv R) Equiv.boolNot

end
end StatMech.FrontierD
