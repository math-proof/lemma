module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part2
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectCutClosedConfiguration
    (R : FKRectTorus) (eta : R.Configuration) : Prop :=
  fkRectForceCutClosed R eta = eta

end
end StatMech.FrontierD
