/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectUnitLeftBarrier
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectUnitLeftBarrierConfiguration (R : FKRectTorus) : R.Configuration :=
  fkRectConfigurationOfEdges R
    ((fkRectHorizontalCutEdges R).erase (fkRectUnitLeftBarrierGap R))

end
end StatMech.FrontierD
