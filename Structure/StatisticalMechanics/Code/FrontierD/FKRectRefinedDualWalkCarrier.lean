/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualOpenWalkCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier.Part3


namespace StatMech.FrontierD

noncomputable section

structure FKRectRefinedDualWalkCarrier
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) where
  darts : List FKRectIntegralSquareDart
  path : FKRectIntegralSquareDartPath
    (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))
    (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)) darts


end
end StatMech.FrontierD
