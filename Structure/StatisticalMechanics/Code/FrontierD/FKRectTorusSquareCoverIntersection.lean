/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Instance.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

structure FKRectSquareCoverCycleWitness (R : FKRectTorus)
    (u : Int × Int) where
  cycle : IntegralSquareTorusCycle (fkRectSquareCoverSide R)
  xFlux_eq : cycle.xFlux (-1) = u.1
  yFlux_eq : cycle.yFlux (-1) = u.2


end
end StatMech.FrontierD
