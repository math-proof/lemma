module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
public import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part4
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectPrimalDualHorizontalCrossingClusterCount_forceCutClosed
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectPrimalDualHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) =
      fkRectPrimalDualHorizontalCrossingClusterCount R omega := by
  simp [fkRectPrimalDualHorizontalCrossingClusterCount]


end
end StatMech.FrontierD
