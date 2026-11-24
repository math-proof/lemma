module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectDualBarrierNetObstructionConfiguration (R : FKRectTorus) :
    R.Configuration :=
  fkRectDualPullbackConfiguration R
    (fkRectUnitLeftBarrierConfiguration R)

end
end StatMech.FrontierD
