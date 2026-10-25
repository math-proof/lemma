/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part2
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectBlackBoundaryCycleWinding
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) : Int × Int :=
  permCycleQuotientWeightSum
    (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega)) C
    (fkRectBlackBoundaryWeight R
      (fkRectConfigurationToMedialPairing R omega))

end
end StatMech.FrontierD
