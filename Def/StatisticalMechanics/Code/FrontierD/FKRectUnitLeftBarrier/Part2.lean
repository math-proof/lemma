module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectUnitLeftBarrier
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectUnitLeftBarrierConfiguration (R : FKRectTorus) : R.Configuration :=
  fkRectConfigurationOfEdges R
    ((fkRectHorizontalCutEdges R).erase (fkRectUnitLeftBarrierGap R))

end
end StatMech.FrontierD
