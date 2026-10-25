/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingRankOneReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutTouch.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutUnits
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

abbrev FKRectHorizontalCutCrossingInFiber
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :=
  {X : {X : (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent //
      FKRectHorizontalCutPrimalCrossingComponent R
        (fkRectForceHorizontalCutClosed R omega) X} //
    fkRectHorizontalCutComponentTorusComponent R omega X.1 = K}

end
end StatMech.FrontierD
