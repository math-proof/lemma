/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPositiveBoundary.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectHorizontalCutComponentTorusComponent_mk
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectHorizontalCutComponentTorusComponent R omega
        ((fkRectOpenGraph R
          (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x) =
      (fkRectOpenGraph R omega).connectedComponentMk x :=
  ConnectedComponent.map_mk _ _


end
end StatMech.FrontierD
