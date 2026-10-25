/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualOpenWalkCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualWalkCarrier


namespace StatMech.FrontierD

noncomputable section

def FKRectRefinedDualWalkCarrier.coverDarts
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (D : FKRectRefinedDualWalkCarrier R h) :=
  fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
    D.darts D.translation


end
end StatMech.FrontierD
