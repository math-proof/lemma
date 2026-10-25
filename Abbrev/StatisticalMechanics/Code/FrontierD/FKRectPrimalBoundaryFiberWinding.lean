/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

abbrev FKRectConfigurationBlackBoundaryCycle
    (R : FKRectTorus) (omega : R.Configuration) :=
  StatMech.FrontierA.PermCycleClass
    (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega))


end
end StatMech.FrontierD
