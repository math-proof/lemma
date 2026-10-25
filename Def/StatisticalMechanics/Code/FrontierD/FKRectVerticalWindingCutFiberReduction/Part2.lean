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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectHorizontalCutComponentTorusComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (X : (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent) :
    (fkRectOpenGraph R omega).ConnectedComponent :=
  ConnectedComponent.map
    (SimpleGraph.Hom.ofLE
      (fkRectOpenGraph_forceHorizontalCutClosed_le R omega)) X

end
end StatMech.FrontierD
