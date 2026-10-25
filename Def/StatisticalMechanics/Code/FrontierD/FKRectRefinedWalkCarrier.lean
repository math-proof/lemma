/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSquareCoverDartList
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier


namespace StatMech.FrontierD

noncomputable section

def FKRectRefinedWalkCarrier.translation
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (_C : FKRectRefinedWalkCarrier R h) : Int × Int :=
  (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
    4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)


end
end StatMech.FrontierD
